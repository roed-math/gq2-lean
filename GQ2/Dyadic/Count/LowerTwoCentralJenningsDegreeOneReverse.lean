/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.LowerTwoCentralJenningsDegreeThree
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteReverse

/-!
# The reverse degree-one Jennings containment for the improved square presentation

This file proves the first reverse containment needed to identify the lower two-central
filtration with the mod-two dimension filtration.  The proof uses the simultaneous elementary
abelian Magnus quotient of `DSq h`: its marked generators are the standard basis, and its
kernel is exactly `lambda_2`.  A character moment kills `I^2`, so a group-like difference in
`I^2` must already come from `lambda_2`.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Roe.Labute
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.LSquare
open scoped commutatorElement

/-- The simultaneous elementary-abelian Magnus quotient is onto. -/
theorem sqMagnusOneHom_surjective (h : ℕ) :
    Function.Surjective (sqMagnusOneHom h) := by
  intro y
  let g : DSq h := (List.ofFn fun i =>
    sqGen h i ^ (Multiplicative.toAdd y i).val).prod
  refine ⟨g, ?_⟩
  apply Multiplicative.toAdd.injective
  funext a
  change Multiplicative.toAdd
      ((sqMagnusOneHom h).toMonoidHom
        (List.ofFn fun i => sqGen h i ^ (Multiplicative.toAdd y i).val).prod) a = _
  rw [map_list_prod, toAdd_list_sum]
  simp only [List.map_ofFn]
  rw [List.sum_ofFn]
  change (∑ i, Multiplicative.toAdd
    (sqMagnusOneHom h (sqGen h i ^ (Multiplicative.toAdd y i).val))) a = _
  rw [Finset.sum_apply]
  simp_rw [map_pow, sqMagnusOneHom_gen, toAdd_pow, sqMagnusOneMark]
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [hba]
  · simp

/-- Squares and commutators die in the simultaneous elementary-abelian Magnus target, so
`lambda_2` lies in its kernel. -/
theorem twoCentralSeries_two_le_sqMagnusOneHom_ker (h : ℕ) :
    twoCentralSeries (DSq h : Type) 2 ≤ (sqMagnusOneHom h).toMonoidHom.ker := by
  rw [twoCentralSeries_succ (DSq h : Type) (by omega), twoCentralSucc]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) ?_
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨v, -, rfl⟩
    change sqMagnusOneHom h (v ^ 2) = 1
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    funext i
    exact GQ2.Dyadic.Count.zmod2_add_self _
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    change sqMagnusOneHom h ⁅a, b⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  · have hset : ((sqMagnusOneHom h).toMonoidHom.ker : Set (DSq h : Type)) =
        (sqMagnusOneHom h) ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact IsClosed.preimage (sqMagnusOneHom h).continuous_toFun isClosed_singleton

/-- The simultaneous first Magnus quotient factored through `DSq h / lambda_2`. -/
noncomputable def sqMagnusOneLevelTwoHom (h : ℕ) :
    levelQuot (DSq h : Type) 2 →* SqMagnusOneTarget h :=
  QuotientGroup.lift (twoCentralSeries (DSq h : Type) 2)
    (sqMagnusOneHom h).toMonoidHom
    (twoCentralSeries_two_le_sqMagnusOneHom_ker h)

@[simp] theorem sqMagnusOneLevelTwoHom_levelMk (h : ℕ) (g : DSq h) :
    sqMagnusOneLevelTwoHom h (levelMk (DSq h : Type) 2 g) = sqMagnusOneHom h g :=
  rfl

/-- The factored simultaneous first Magnus quotient is onto. -/
theorem sqMagnusOneLevelTwoHom_surjective (h : ℕ) :
    Function.Surjective (sqMagnusOneLevelTwoHom h) := by
  intro y
  obtain ⟨g, rfl⟩ := sqMagnusOneHom_surjective h y
  exact ⟨levelMk (DSq h : Type) 2 g, rfl⟩

/-- The source and target of the factored simultaneous first Magnus quotient have the same
finite cardinality. -/
theorem card_levelQuot_two_eq_card_sqMagnusOneTarget (h : ℕ) :
    Nat.card (levelQuot (DSq h : Type) 2) = Nat.card (SqMagnusOneTarget h) := by
  calc
    Nat.card (levelQuot (DSq h : Type) 2) =
        Nat.card (zLayer (DSq h : Type) 1) := by
      rw [zLayer_one_eq_top]
      exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
    _ = 2 ^ sqRank h := card_zLayer_one_dsq h
    _ = Nat.card (SqMagnusOneTarget h) := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
        Nat.card_zmod]

/-- The simultaneous first Magnus quotient identifies `DSq h / lambda_2` with its literal
elementary-abelian marked target. -/
theorem sqMagnusOneLevelTwoHom_bijective (h : ℕ) :
    Function.Bijective (sqMagnusOneLevelTwoHom h) := by
  letI : Finite (levelQuot (DSq h : Type) 2) :=
    finite_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 2
  apply (Nat.bijective_iff_surjective_and_card _).2
  exact ⟨sqMagnusOneLevelTwoHom_surjective h,
    card_levelQuot_two_eq_card_sqMagnusOneTarget h⟩

/-- The kernel of the simultaneous elementary-abelian Magnus quotient is exactly
`lambda_2(DSq h)`. -/
theorem twoCentralSeries_two_eq_sqMagnusOneKernel (h : ℕ) :
    twoCentralSeries (DSq h : Type) 2 = (sqMagnusOneKernel h).toSubgroup := by
  apply le_antisymm
  · exact twoCentralSeries_two_le_sqMagnusOneHom_ker h
  · intro g hg
    have hmap : sqMagnusOneHom h g = 1 := MonoidHom.mem_ker.mp hg
    have hlevel : levelMk (DSq h : Type) 2 g = 1 :=
      (sqMagnusOneLevelTwoHom_bijective h).injective (by simpa using hmap)
    exact (QuotientGroup.eq_one_iff g).mp hlevel

/-- Every mod-two character kills a group element whose group-like difference has
augmentation order at least two. -/
theorem character_eq_one_of_groupDifference_mem_augmentation_sq
    {Q : Type} [Group Q] (chi : Q →* Multiplicative (ZMod 2)) (q : Q)
    (hq : modTwoFiniteGroupDifference Q q ∈ modTwoFiniteAugmentationIdeal Q ^ 2) :
    chi q = 1 := by
  have hzero := modTwoGroupAlgebraLinearMoment_eq_zero_of_mem_augmentation_sq chi hq
  rw [modTwoFiniteGroupDifference, map_sub,
    modTwoGroupAlgebraLinearMoment_of] at hzero
  have hone : modTwoGroupAlgebraLinearMoment chi
      (1 : MonoidAlgebra (ZMod 2) Q) = 0 := by
    rw [MonoidAlgebra.one_def, modTwoGroupAlgebraLinearMoment_single]
    simp
  rw [hone, sub_zero] at hzero
  apply Multiplicative.toAdd.injective
  simpa using hzero

/-- The simultaneous first Magnus quotient also factors through the common fourth
lower-two-central quotient. -/
noncomputable def sqMagnusOneFourthHom (h : ℕ) :
    SqFourthLevel h →* SqMagnusOneTarget h :=
  QuotientGroup.lift (twoCentralSeries (DSq h : Type) 4)
    (sqMagnusOneHom h).toMonoidHom
    ((twoCentralSeries_antitone (DSq h : Type) (by omega : 2 ≤ 4)).trans
      (twoCentralSeries_two_le_sqMagnusOneHom_ker h))

@[simp] theorem sqMagnusOneFourthHom_levelMk (h : ℕ) (g : DSq h) :
    sqMagnusOneFourthHom h (levelMk (DSq h : Type) 4 g) = sqMagnusOneHom h g :=
  rfl

/-- **Reverse Jennings containment in degree one for the common finite quotient.**  If
`[q]-1` has augmentation order at least two in `F_2[Q_4]`, then `q` lies in
`lambda_2(Q_4)`. -/
theorem modTwoFiniteDimensionSubgroup_two_le_twoCentralSeries_sqFourthLevel (h : ℕ) :
    modTwoFiniteDimensionSubgroup (SqFourthLevel h) 2 ≤
      twoCentralSeries (SqFourthLevel h) 2 := by
  letI : DiscreteTopology (SqFourthLevel h) :=
    discreteTopology_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  letI : Finite (SqFourthLevel h) :=
    finite_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  intro q hq
  have hfirst : sqMagnusOneFourthHom h q = 1 := by
    apply Multiplicative.toAdd.injective
    funext a
    let chi : SqFourthLevel h →* Multiplicative (ZMod 2) :=
      (multiplicativeModTwoCharacter (sqMagnusOneCoordinate h a)).comp
        (sqMagnusOneFourthHom h)
    have hchi := character_eq_one_of_groupDifference_mem_augmentation_sq chi q hq
    have hchiAdd := congrArg Multiplicative.toAdd hchi
    simpa [chi, multiplicativeModTwoCharacter, sqMagnusOneCoordinate] using hchiAdd
  obtain ⟨g, rfl⟩ := levelMk_surjective (DSq h : Type) 4 q
  have hgker : g ∈ (sqMagnusOneKernel h).toSubgroup := by
    apply MonoidHom.mem_ker.mpr
    simpa using hfirst
  have hg : g ∈ twoCentralSeries (DSq h : Type) 2 := by
    rw [twoCentralSeries_two_eq_sqMagnusOneKernel h]
    exact hgker
  exact map_twoCentralSeries_le (levelMk (DSq h : Type) 4)
    (continuous_levelMk (DSq h : Type) 4) 2 ⟨g, hg, rfl⟩

/-- Thus degree two of the dimension filtration and lower two-central filtration agree on
`Q_4`. -/
theorem modTwoFiniteDimensionSubgroup_two_eq_twoCentralSeries_sqFourthLevel (h : ℕ) :
    modTwoFiniteDimensionSubgroup (SqFourthLevel h) 2 =
      twoCentralSeries (SqFourthLevel h) 2 := by
  letI : DiscreteTopology (SqFourthLevel h) :=
    discreteTopology_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  letI : Finite (SqFourthLevel h) :=
    finite_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  exact le_antisymm
    (modTwoFiniteDimensionSubgroup_two_le_twoCentralSeries_sqFourthLevel h)
    (twoCentralSeries_le_modTwoFiniteDimensionSubgroup (SqFourthLevel h) 2)

/-- A degree-one `DSq` layer class whose fourth-level lift has augmentation order two is
trivial. -/
theorem dsqZLayerFourthLift_mem_dimension_two_imp_eq_one (h : ℕ)
    (z : zLayer (DSq h : Type) 1)
    (hz : dsqZLayerFourthLift h 1 z ∈
      modTwoFiniteDimensionSubgroup (SqFourthLevel h) 2) :
    z = 1 := by
  letI : DiscreteTopology (SqFourthLevel h) :=
    discreteTopology_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  letI : Finite (SqFourthLevel h) :=
    finite_levelQuot (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 4
  have hlift : dsqZLayerFourthLift h 1 z ∈
      twoCentralSeries (SqFourthLevel h) 2 :=
    modTwoFiniteDimensionSubgroup_two_le_twoCentralSeries_sqFourthLevel h hz
  rw [← lambdaImage_eq_twoCentralSeries_levelQuot
    (DSq h : Type) (dsqFinsetTopGen h) (isProP_DSq h) 2 4] at hlift
  obtain ⟨u, hu, hulift⟩ := hlift
  apply Subtype.ext
  rw [← levelMk_dsqZLayerRepresentative h 1 z]
  change levelMk (DSq h : Type) 2 (dsqZLayerRepresentative h 1 z) = 1
  apply (QuotientGroup.eq_one_iff (dsqZLayerRepresentative h 1 z)).mpr
  have hsame : dsqZLayerRepresentative h 1 z * u⁻¹ ∈
      twoCentralSeries (DSq h : Type) 4 := by
    apply (QuotientGroup.eq_one_iff
      (dsqZLayerRepresentative h 1 z * u⁻¹)).mp
    change levelMk (DSq h : Type) 4
      (dsqZLayerRepresentative h 1 z * u⁻¹) = 1
    rw [map_mul, map_inv]
    change dsqZLayerFourthLift h 1 z * (levelMk (DSq h : Type) 4 u)⁻¹ = 1
    rw [hulift]
    exact mul_inv_cancel _
  have hsameTwo :=
    (twoCentralSeries_antitone (DSq h : Type) (by omega : 2 ≤ 4)) hsame
  simpa [mul_assoc] using
    (twoCentralSeries (DSq h : Type) 2).mul_mem hsameTwo hu

/-- The degree-one lower-two-central-to-augmentation-layer map is injective. -/
theorem dsqZLayerOneToFourthAugmentationLayer_injective (h : ℕ) :
    Function.Injective (dsqZLayerOneToFourthAugmentationLayer h) := by
  apply (injective_iff_map_eq_zero (dsqZLayerOneToFourthAugmentationLayer h)).2
  intro z hz
  apply Additive.toMul.injective
  apply dsqZLayerFourthLift_mem_dimension_two_imp_eq_one h z.toMul
  exact (dsqZLayerToFourthAugmentationLayer_eq_zero_iff h 1 (by omega) z).1 hz

#print axioms twoCentralSeries_two_eq_sqMagnusOneKernel
#print axioms modTwoFiniteDimensionSubgroup_two_eq_twoCentralSeries_sqFourthLevel
#print axioms dsqZLayerOneToFourthAugmentationLayer_injective

end

end GQ2.ContCoh
