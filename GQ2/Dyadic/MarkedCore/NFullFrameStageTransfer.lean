import GQ2.Dyadic.MarkedCore.NFullFrameCompactness
import GQ2.Dyadic.MarkedCore.NPlaneFreeStageTransfer
import GQ2.Dyadic.MarkedCore.FreeProTwoMatrixBasis

/-!
# Full-coordinate transfer of arbitrary free N stages

Exact integral coordinates on the free group determine the image under every
commutative pro-two map. Applying this to the full topological abelianization
retains torsion as well as every free coordinate. Thus no plane-only predicate
or torsion-invisible character quotient is substituted in the limit argument.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 GQ2.SectionThree Multiplicative Roe.Labute
open scoped GQ2.SectionThree.TopAbInstances

theorem freeNProjection_ab_eq_of_coordinates (alpha h : ℕ)
    (x y : FreeTwoRank (coreRank h))
    (hxy : ∀ j, toAdd (freeTwoCoordinate (coreRank h) j x) =
      toAdd (freeTwoCoordinate (coreRank h) j y)) :
    abMk (freeNProjection alpha h x) = abMk (freeNProjection alpha h y) := by
  let a : ContinuousMonoidHom (DN alpha h : Type)
      (topAbelianization (DN alpha h : Type)) :=
    { toMonoidHom := abMk, continuous_toFun := continuous_abMk }
  exact freeTwo_commutative_eq_of_coordinates (nIsProP_two_topAb_DN alpha h)
    (coreRank h) x y hxy (a.comp (freeNProjection alpha h))

theorem nPhiHom_freeNProjection_eq_of_coordinates {alpha h : ℕ} (ha : 2 ≤ alpha)
    (x y : FreeTwoRank (coreRank h))
    (hxy : ∀ j, toAdd (freeTwoCoordinate (coreRank h) j x) =
      toAdd (freeTwoCoordinate (coreRank h) j y)) :
    nPhiHom ha h (abMk (freeNProjection alpha h x)) =
      nPhiHom ha h (abMk (freeNProjection alpha h y)) :=
  congrArg (nPhiHom ha h) (freeNProjection_ab_eq_of_coordinates alpha h x y hxy)

theorem nFullFrame_modTwoIndep_of_freeBasis (alpha h : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type)) :
    NPlaneModTwoIndep alpha h
      (fun i => freeNProjection alpha h (e (freeTwoRankGen (coreRank h) i))) := by
  intro M hM
  by_contra hc
  have hmem : ∀ i, freeNProjection alpha h (e (freeTwoRankGen (coreRank h) i)) ∈ M.toSubgroup :=
    fun i => not_not.mp fun hi => hc ⟨i, hi⟩
  let f := (freeNProjection alpha h).comp (autHom e)
  have hclosed : IsClosed ((M.toSubgroup.comap f.toMonoidHom :
      Subgroup (FreeTwoRank (coreRank h) : Type)) : Set (FreeTwoRank (coreRank h) : Type)) :=
    (Subgroup.isClosed_of_isOpen _ M.isOpen').preimage f.continuous_toFun
  have hle : Subgroup.closure (Set.range (freeTwoRankGen (coreRank h))) ≤
      M.toSubgroup.comap f.toMonoidHom :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  have htop := Subgroup.topologicalClosure_minimal _ hle hclosed
  rw [show (Subgroup.closure (Set.range (freeTwoRankGen (coreRank h)))).topologicalClosure = ⊤
    from presPro2_topGen 1] at htop
  have hf : Function.Surjective f := (freeNProjection_surjective alpha h).comp e.surjective
  have hMtop : M.toSubgroup = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro z
    obtain ⟨x, rfl⟩ := hf z
    exact htop (Subgroup.mem_top x)
  rw [hMtop, Subgroup.index_top] at hM
  omega

/-- Transfer an actual free stage with arbitrary exact initial columns to a
stage with every literal N abelianization coordinate, including torsion. -/
theorem nFullFrameStageSet_of_free_exact_stage {alpha h : ℕ} (ha : 2 ≤ alpha)
    (k : ℕ) (initial : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (hchi : ∀ i, freeNOrientation alpha h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation alpha h (freeTwoRankGen (coreRank h) i))
    (hcoord : ∀ j i, toAdd (freeTwoCoordinate (coreRank h) j
      (e (freeTwoRankGen (coreRank h) i))) =
        toAdd (freeTwoCoordinate (coreRank h) j (initial i)))
    (herr : nRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (nRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) k) :
    (fun i => freeNProjection alpha h (e (freeTwoRankGen (coreRank h) i))) ∈
      nFullFrameStageSet ha
        (fun i => nPhiHom ha h (abMk (freeNProjection alpha h (initial i)))) k := by
  refine ⟨?_, ?_, nFullFrame_modTwoIndep_of_freeBasis alpha h e, ?_⟩
  · intro i
    rw [freeNProjection_orientation, hchi, ← freeNProjection_orientation, freeNProjection_gen]
  · intro i
    exact nPhiHom_freeNProjection_eq_of_coordinates ha _ _ (fun j => hcoord j i)
  · have hh := map_twoCentralSeries_le (freeNProjection alpha h).toMonoidHom
      (freeNProjection alpha h).continuous_toFun k ⟨_, herr, rfl⟩
    change freeNProjection alpha h _ ∈ twoCentralSeries (DN alpha h : Type) k at hh
    rw [map_mul, map_inv, map_nRelWord, map_nRelWord] at hh
    simp only [freeNProjection_gen, dn_relation, inv_one, mul_one] at hh
    exact hh

#print axioms freeNProjection_ab_eq_of_coordinates
#print axioms nPhiHom_freeNProjection_eq_of_coordinates
#print axioms nFullFrame_modTwoIndep_of_freeBasis
#print axioms nFullFrameStageSet_of_free_exact_stage

end
end GQ2.Dyadic.MarkedCore
