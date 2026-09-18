import GQ2.Dyadic.MarkedCore.NPlaneCompactness
import GQ2.Dyadic.MarkedCore.NPlaneKernelDiagonal

/-!
# Transfer of supplied exact-row free stages to the N quotient

This is a conditional transfer: an actual free automorphism supplies the
basis, exact coordinate and orientation equations supply its marking, and
an actual filtered relator defect supplies the stage. No stage existence or
unrestricted derivative-image theorem is asserted.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

def freeNProjection (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (DN α h : Type) :=
  presLiftHom 1 (isProP_DN α h) (dnGen α h) (map_one _)

theorem freeNProjection_gen (α h : ℕ) (i : Fin (coreRank h)) :
    freeNProjection α h (freeTwoRankGen (coreRank h) i) = dnGen α h i :=
  presLiftHom_gen _ _ _ _ _

theorem freeNProjection_surjective (α h : ℕ) : Function.Surjective (freeNProjection α h) := by
  have hle : Subgroup.closure (Set.range (dnGen α h)) ≤ (freeNProjection α h).range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨freeTwoRankGen (coreRank h) i, freeNProjection_gen α h i⟩
  have hh := Subgroup.topologicalClosure_minimal _ hle
    (isCompact_range (freeNProjection α h).continuous_toFun).isClosed
  rw [dn_topGen α h] at hh
  exact MonoidHom.range_eq_top.mp (top_unique hh)

theorem freeNProjection_orientation (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    chiN α h (freeNProjection α h x) = freeNOrientation α h x := by
  have he : (chiN α h).comp (freeNProjection α h) = freeNOrientation α h := by
    apply presPro2_hom_ext
    intro i
    change chiN α h (freeNProjection α h (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) i)
    rw [freeNProjection_gen, chiN, nLiftHom_gen, freeNOrientation_gen]
    have hi : (i : ℕ) = 1 ↔ i = 1 := by
      rw [← coreVal_one (h := h)]
      exact Fin.val_injective.eq_iff
    by_cases hz : (i : ℕ) = 0
    · have hn : i ≠ 1 := by intro he; rw [he, coreVal_one] at hz; omega
      simp [coreMark, hz, hn]
    · simp [coreMark, hz, hi]
  exact congrArg (fun f : ContinuousMonoidHom _ _ => f x) he

private theorem projection_basis_modTwo (α h : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type)) :
    NPlaneModTwoIndep α h (fun i => freeNProjection α h (e (freeTwoRankGen (coreRank h) i))) := by
  intro M hM
  by_contra hc
  have hmem : ∀ i, freeNProjection α h (e (freeTwoRankGen (coreRank h) i)) ∈ M.toSubgroup :=
    fun i => not_not.mp fun hi => hc ⟨i, hi⟩
  let f := (freeNProjection α h).comp (autHom e)
  have hclosed : IsClosed ((M.toSubgroup.comap f.toMonoidHom :
      Subgroup (FreeTwoRank (coreRank h) : Type)) : Set (FreeTwoRank (coreRank h) : Type)) :=
    (Subgroup.isClosed_of_isOpen _ M.isOpen').preimage f.continuous_toFun
  have hle : Subgroup.closure (Set.range (freeTwoRankGen (coreRank h))) ≤
      M.toSubgroup.comap f.toMonoidHom :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  have htop := Subgroup.topologicalClosure_minimal _ hle hclosed
  rw [show (Subgroup.closure (Set.range (freeTwoRankGen (coreRank h)))).topologicalClosure = ⊤
    from presPro2_topGen 1] at htop
  have hf : Function.Surjective f := (freeNProjection_surjective α h).comp e.surjective
  have hMtop : M.toSubgroup = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro z
    obtain ⟨x, rfl⟩ := hf z
    exact htop (Subgroup.mem_top x)
  rw [hMtop, Subgroup.index_top] at hM
  omega

/-- Supplied exact free stages yield the actual quotient stages consumed by
NPlaneCompactness, with every ordinary character quantified after the basis. -/
theorem nPlaneStageSet_of_free_exact_stage (α h k : ℕ) (κ : ℤ_[2]ˣ)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (hchi : ∀ i, freeNOrientation α h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation α h (freeTwoRankGen (coreRank h) i))
    (hcoord : ∀ j i, toAdd (freeTwoCoordinate (coreRank h) j
      (e (freeTwoRankGen (coreRank h) i))) =
        if j=i then (freeTwoUnitPowerWeights (coreRank h) 2 κ i : ℤ_[2]) else 0)
    (herr : nRelWord α (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (nRelWord α (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) k) :
    (fun i => freeNProjection α h (e (freeTwoRankGen (coreRank h) i))) ∈
      nPlaneStageSet α h (nPlaneDet κ) k := by
  refine ⟨?_, ?_, projection_basis_modTwo α h e, ?_⟩
  · intro i
    rw [freeNProjection_orientation, hchi, ← freeNProjection_orientation, freeNProjection_gen]
  · intro f
    have hv : ∀ i, toAdd (f (freeNProjection α h (e (freeTwoRankGen (coreRank h) i)))) =
        (freeTwoUnitPowerWeights (coreRank h) 2 κ i : ℤ_[2]) * toAdd (f (dnGen α h i)) := by
      intro i
      have he := freeTwo_character_coordinates (coreRank h) (f.comp (freeNProjection α h))
        (e (freeTwoRankGen (coreRank h) i))
      simpa [hcoord, freeNProjection_gen] using he
    funext i
    change toAdd (f (freeNProjection α h (e (freeTwoRankGen (coreRank h) i)))) = _
    rw [hv]
    by_cases h2 : i = 2
    · subst i
      simp [nCoreMat_two, nPlaneDet, freeTwoUnitPowerWeights, nuFrame, smul_eq_mul]
    · by_cases h3 : i = 3
      · subst i
        simp [nCoreMat_three, nPlaneDet, freeTwoUnitPowerWeights, nuFrame, h2]
      · rw [nCoreMat_of_ne _ _ h2 h3]
        simp [freeTwoUnitPowerWeights, h2, nuFrame]
  · have hh := map_twoCentralSeries_le (freeNProjection α h).toMonoidHom
      (freeNProjection α h).continuous_toFun k ⟨_, herr, rfl⟩
    change freeNProjection α h _ ∈ twoCentralSeries (DN α h : Type) k at hh
    rw [map_mul, map_inv, map_nRelWord, map_nRelWord] at hh
    simp only [freeNProjection_gen, dn_relation, inv_one, mul_one] at hh
    exact hh

#print axioms freeNProjection
#print axioms freeNProjection_gen
#print axioms freeNProjection_surjective
#print axioms freeNProjection_orientation
#print axioms nPlaneStageSet_of_free_exact_stage

end
end GQ2.Dyadic.MarkedCore
