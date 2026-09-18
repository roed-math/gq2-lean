import GQ2.Dyadic.MarkedCore.FreeProTwoCharacterCorrection

/-!
# Initial unit-power substitutions in free pro-two groups

The selected generator is raised to an arbitrary two-adic unit, and every
other generator is fixed. This is a free-group automorphism. For a non-head
generator of the N word, its initial relator error has filtration depth three
and is killed by every ordinary character. No N-boundary preservation or
automorphism of the N quotient is asserted.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative
open GQ2.Roe.Labute

def freeTwoUnitPowerMark (n : ℕ) (c : Fin n) (κ : ℤ_[2]ˣ) (i : Fin n) :
    FreeTwoRank n :=
  if i = c then zpowZtwo (isProP_presPro2 1) (freeTwoRankGen n c) (κ : ℤ_[2])
  else freeTwoRankGen n i

def freeTwoUnitPowerHom (n : ℕ) (c : Fin n) (κ : ℤ_[2]ˣ) :
    ContinuousMonoidHom (FreeTwoRank n : Type) (FreeTwoRank n : Type) :=
  presLiftHom 1 (isProP_presPro2 1) (freeTwoUnitPowerMark n c κ) (map_one _)

theorem freeTwoUnitPowerHom_gen (n : ℕ) (c i : Fin n) (κ : ℤ_[2]ˣ) :
    freeTwoUnitPowerHom n c κ (freeTwoRankGen n i) = freeTwoUnitPowerMark n c κ i :=
  presLiftHom_gen _ _ _ _ _

theorem freeTwoUnitPowerHom_comp_inv (n : ℕ) (c : Fin n) (κ : ℤ_[2]ˣ) :
    (freeTwoUnitPowerHom n c κ).comp (freeTwoUnitPowerHom n c κ⁻¹) =
      ContinuousMonoidHom.id (FreeTwoRank n : Type) := by
  apply presPro2_hom_ext
  intro i
  change freeTwoUnitPowerHom n c κ (freeTwoUnitPowerHom n c κ⁻¹
    (freeTwoRankGen n i)) = freeTwoRankGen n i
  rw [freeTwoUnitPowerHom_gen, freeTwoUnitPowerMark]
  split_ifs with hi
  · subst i
    rw [map_zpowZtwo (isProP_presPro2 1) (isProP_presPro2 1),
      freeTwoUnitPowerHom_gen, freeTwoUnitPowerMark, if_pos rfl,
      zpowZtwo_zpowZtwo]
    simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, zpowZtwo_one_exp]
  · rw [freeTwoUnitPowerHom_gen, freeTwoUnitPowerMark, if_neg hi]

def freeTwoUnitPowerEquiv (n : ℕ) (c : Fin n) (κ : ℤ_[2]ˣ) :
    ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type) :=
  continuousMulEquivOfBijective (freeTwoUnitPowerHom n c κ)
    (Function.bijective_iff_has_inverse.mpr ⟨freeTwoUnitPowerHom n c κ⁻¹,
      fun x => by
        have he := freeTwoUnitPowerHom_comp_inv n c κ⁻¹
        simpa using congrArg (fun f : ContinuousMonoidHom _ _ => f x) he,
      fun x => congrArg (fun f : ContinuousMonoidHom _ _ => f x)
        (freeTwoUnitPowerHom_comp_inv n c κ)⟩)

theorem freeTwoUnitPowerEquiv_gen (n : ℕ) (c i : Fin n) (κ : ℤ_[2]ˣ) :
    freeTwoUnitPowerEquiv n c κ (freeTwoRankGen n i) = freeTwoUnitPowerMark n c κ i :=
  freeTwoUnitPowerHom_gen n c i κ

/-- One automorphism has these rows simultaneously for every character. -/
theorem freeTwoUnitPowerEquiv_character_gen (n : ℕ) (c i : Fin n) (κ : ℤ_[2]ˣ)
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2])) :
    toAdd (f (freeTwoUnitPowerEquiv n c κ (freeTwoRankGen n i))) =
      if i = c then (κ : ℤ_[2]) * toAdd (f (freeTwoRankGen n c))
      else toAdd (f (freeTwoRankGen n i)) := by
  rw [freeTwoUnitPowerEquiv_gen, freeTwoUnitPowerMark]
  split_ifs
  · exact toAdd_map_zpowZtwo (isProP_presPro2 1) f _ _
  · rfl

theorem freeTwoUnitPowerEquiv_character (n : ℕ) (c : Fin n) (κ : ℤ_[2]ˣ)
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]))
    (x : FreeTwoRank n) :
    toAdd (f (freeTwoUnitPowerEquiv n c κ x)) =
      ∑ i, toAdd (freeTwoCoordinate n i x) *
        (if i = c then (κ : ℤ_[2]) * toAdd (f (freeTwoRankGen n c))
        else toAdd (f (freeTwoRankGen n i))) := by
  have he := freeTwo_character_coordinates n (f.comp (freeTwoUnitPowerHom n c κ)) x
  change toAdd (f (freeTwoUnitPowerEquiv n c κ x)) =
    ∑ i, toAdd (freeTwoCoordinate n i x) *
      toAdd (f (freeTwoUnitPowerEquiv n c κ (freeTwoRankGen n i))) at he
  simpa only [freeTwoUnitPowerEquiv_character_gen] using he

private theorem unitPowerMark_eq_layer_two_mul (n : ℕ) (c i : Fin n) (κ : ℤ_[2]ˣ) :
    ∃ z ∈ twoCentralSeries (FreeTwoRank n : Type) 2,
      freeTwoUnitPowerMark n c κ i = z * freeTwoRankGen n i := by
  classical
  by_cases hi : i = c
  · subst i
    obtain ⟨t, ht⟩ := two_dvd_val_sub_one κ
    have he : (κ : ℤ_[2]) = t * 2 + 1 := by linear_combination ht
    refine ⟨(zpowZtwo (isProP_presPro2 1) (freeTwoRankGen n c) t)^2,
      sq_mem_twoCentralSeries_succ _ (by simp), ?_⟩
    rw [freeTwoUnitPowerMark, if_pos rfl, he, zpowZtwo_add, zpowZtwo_one_exp,
      ← zpowZtwo_natCast (isProP_presPro2 1) _ 2, zpowZtwo_zpowZtwo]
    norm_num
  · exact ⟨1, Subgroup.one_mem _, by simp [freeTwoUnitPowerMark, hi]⟩

private theorem unitPowerMark_comm_level_three (n : ℕ) (c i j : Fin n) (κ : ℤ_[2]ˣ) :
    commP (levelMk (FreeTwoRank n : Type) 3 (freeTwoUnitPowerMark n c κ i))
      (levelMk (FreeTwoRank n : Type) 3 (freeTwoUnitPowerMark n c κ j)) =
    commP (levelMk (FreeTwoRank n : Type) 3 (freeTwoRankGen n i))
      (levelMk (FreeTwoRank n : Type) 3 (freeTwoRankGen n j)) := by
  obtain ⟨z, hz, he⟩ := unitPowerMark_eq_layer_two_mul n c i κ
  obtain ⟨w, hw, hf⟩ := unitPowerMark_eq_layer_two_mul n c j κ
  have hzc : levelMk (FreeTwoRank n : Type) 3 z ∈
      Subgroup.center (levelQuot (FreeTwoRank n : Type) 3) :=
    zLayer_le_center _ 2 ⟨z, hz, rfl⟩
  have hwc : levelMk (FreeTwoRank n : Type) 3 w ∈
      Subgroup.center (levelQuot (FreeTwoRank n : Type) 3) :=
    zLayer_le_center _ 2 ⟨w, hw, rfl⟩
  rw [he, hf, map_mul, map_mul,
    commP_pre_mul_left_of_commute (show Commute (levelMk _ 3 z) _ from
      (Subgroup.mem_center_iff.mp hzc _).symm),
    commP_pre_mul_right_of_commute (show Commute _ (levelMk _ 3 w) from
      Subgroup.mem_center_iff.mp hwc _)]

def nInitialUnitPowerError (α h : ℕ) (c : Fin (coreRank h)) (κ : ℤ_[2]ˣ) :
    FreeTwoRank (coreRank h) :=
  nRelWord α (freeTwoUnitPowerMark (coreRank h) c κ) *
    (nRelWord α (freeTwoRankGen (coreRank h)))⁻¹

theorem nInitialUnitPowerError_mem_three (α h : ℕ) (c : Fin (coreRank h))
    (hc : c ≠ 0) (κ : ℤ_[2]ˣ) :
    nInitialUnitPowerError α h c κ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3 := by
  have he : levelMk (FreeTwoRank (coreRank h) : Type) 3
      (nRelWord α (freeTwoUnitPowerMark (coreRank h) c κ)) =
      levelMk (FreeTwoRank (coreRank h) : Type) 3
      (nRelWord α (freeTwoRankGen (coreRank h))) := by
    rw [map_nRelWord, map_nRelWord]
    unfold nRelWord nWord
    rw [unitPowerMark_comm_level_three, unitPowerMark_comm_level_three]
    have hh : freeTwoUnitPowerMark (coreRank h) c κ 0 = freeTwoRankGen (coreRank h) 0 :=
      if_neg (Ne.symm hc)
    dsimp only
    rw [hh]
    congr 1
    unfold handleWord
    congr 1
    apply List.map_congr_left
    intro j _
    exact unitPowerMark_comm_level_three _ _ _ _ _
  apply (QuotientGroup.eq_one_iff _).mp
  change levelMk (FreeTwoRank (coreRank h) : Type) 3
    (nInitialUnitPowerError α h c κ) = 1
  rw [nInitialUnitPowerError, map_mul, map_inv, he, mul_inv_cancel]

/-- The initial error actually vanishes in every abelian target, not only in
ordinary Z2 characters. This is exact full abelianization, not a mod-two row. -/
theorem nInitialUnitPowerError_commutative {Q : Type*} [CommGroup Q]
    (α h : ℕ) (c : Fin (coreRank h)) (hc : c ≠ 0) (κ : ℤ_[2]ˣ)
    (f : (FreeTwoRank (coreRank h) : Type) →* Q) :
    f (nInitialUnitPowerError α h c κ) = 1 := by
  rw [nInitialUnitPowerError, map_mul, map_inv, map_nRelWord, map_nRelWord,
    nRelWord_comm, nRelWord_comm]
  simp [freeTwoUnitPowerMark, Ne.symm hc]

theorem nInitialUnitPowerError_character (α h : ℕ) (c : Fin (coreRank h))
    (hc : c ≠ 0) (κ : ℤ_[2]ˣ)
    (f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (Multiplicative ℤ_[2])) :
    f (nInitialUnitPowerError α h c κ) = 1 :=
  nInitialUnitPowerError_commutative α h c hc κ f.toMonoidHom

#print axioms freeTwoUnitPowerMark
#print axioms freeTwoUnitPowerHom
#print axioms freeTwoUnitPowerHom_gen
#print axioms freeTwoUnitPowerHom_comp_inv
#print axioms freeTwoUnitPowerEquiv
#print axioms freeTwoUnitPowerEquiv_gen
#print axioms freeTwoUnitPowerEquiv_character_gen
#print axioms freeTwoUnitPowerEquiv_character
#print axioms nInitialUnitPowerError
#print axioms nInitialUnitPowerError_mem_three
#print axioms nInitialUnitPowerError_commutative
#print axioms nInitialUnitPowerError_character

end
end GQ2.Dyadic.MarkedCore
