import GQ2.Dyadic.MarkedCore.NBasisExactStages
import GQ2.Dyadic.MarkedCore.NFullFrameStageTransfer

/-!
# Arbitrary full N markings reduce to one actual initial depth-three basis

All higher filtered corrections and the torsion-sensitive compact limit are
constructed here. The initial free basis, exact orientation/relator row and
literal depth-three error are explicit inputs. In particular this does not
assume that a cup isometry has already supplied the initial error.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 GQ2.SectionThree Multiplicative Roe.Labute
open scoped GQ2.SectionThree.TopAbInstances

theorem exists_nFullFrameRealizes_of_initialBasis {alpha h : ℕ} (ha : 2 ≤ alpha)
    (e0 : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (hchi0 : ∀ i, freeNOrientation alpha h (e0 (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation alpha h (freeTwoRankGen (coreRank h) i))
    (hrow0 : ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]),
      f (nRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i))) =
        f (nRelWord alpha (freeTwoRankGen (coreRank h))))
    (herror0 : nRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i)) *
      (nRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      NFullFrameRealizes ha Psi (fun i => nPhiHom ha h
        (abMk (freeNProjection alpha h (e0 (freeTwoRankGen (coreRank h) i))))) := by
  apply exists_nFullFrameRealizes_of_stages
  intro k
  obtain ⟨e, hechi, hecoords, heerror⟩ :=
    exists_nBasis_exact_stage ha e0 hchi0 hrow0 herror0 k
  refine ⟨fun i => freeNProjection alpha h (e (freeTwoRankGen (coreRank h) i)), ?_⟩
  exact nFullFrameStageSet_antitone ha _ (by omega : k ≤ k+3)
    (nFullFrameStageSet_of_free_exact_stage ha (k+3)
      (fun i => e0 (freeTwoRankGen (coreRank h) i)) e hechi hecoords heerror)

/-- Literal head fixation supplies the exact ordinary relator row automatically.
The initial depth-three comparison remains a genuine hypothesis. -/
theorem exists_nFullFrameRealizes_of_headFixed_initialBasis {alpha h : ℕ} (ha : 2 ≤ alpha)
    (e0 : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (hhead : e0 (freeTwoRankGen (coreRank h) 0) = freeTwoRankGen (coreRank h) 0)
    (hchi0 : ∀ i, freeNOrientation alpha h (e0 (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation alpha h (freeTwoRankGen (coreRank h) i))
    (herror0 : nRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i)) *
      (nRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      NFullFrameRealizes ha Psi (fun i => nPhiHom ha h
        (abMk (freeNProjection alpha h (e0 (freeTwoRankGen (coreRank h) i))))) := by
  apply exists_nFullFrameRealizes_of_initialBasis ha e0 hchi0 _ herror0
  intro f
  apply toAdd.injective
  rw [nRelWord_ordinary_row, nRelWord_ordinary_row, hhead]

theorem freeNProjection_ab_coordinateWord (alpha h : ℕ)
    (c : Fin (coreRank h) → ℤ_[2]) :
    abMk (freeNProjection alpha h (freeTwoCoordinateWord (coreRank h) c)) =
      nAbWord alpha h c := by
  let a : ContinuousMonoidHom (DN alpha h : Type)
      (topAbelianization (DN alpha h : Type)) :=
    { toMonoidHom := abMk, continuous_toFun := continuous_abMk }
  let f := a.comp (freeNProjection alpha h)
  change f (freeTwoCoordinateWord (coreRank h) c) = _
  rw [freeTwo_commutative_hom_coordinates (nIsProP_two_topAb_DN alpha h),
    nAbWord]
  apply Finset.prod_congr rfl
  intro i _
  rw [freeTwoCoordinateWord_coordinate]
  have hi : f (freeTwoRankGen (coreRank h) i) = abMk (dnGen alpha h i) := by
    change abMk (freeNProjection alpha h (freeTwoRankGen (coreRank h) i)) = _
    rw [freeNProjection_gen]
  rw [hi]

/-- Matrix-shaped interface for the remaining initial cup/depth calculation.
The head column and orientation row are exact integral equalities. No diagonal
or identity-handle hypothesis occurs, and all higher stages are supplied. -/
theorem exists_nFullFrameRealizes_of_matrix_initial_error {alpha h : ℕ} (ha : 2 ≤ alpha)
    (A B : Matrix (Fin (coreRank h)) (Fin (coreRank h)) ℤ_[2])
    (hAB : A * B = 1)
    (hhead : ∀ j, A j 0 = if j = 0 then 1 else 0)
    (hchi : ∀ i, A 1 i = if i = 1 then 1 else 0)
    (herror : nRelWord alpha
        (fun i => freeTwoCoordinateWord (coreRank h) (fun j => A j i)) *
      (nRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      NFullFrameRealizes ha Psi (fun i => nPhiHom ha h
        (nAbWord alpha h (fun j => A j i))) := by
  let e := freeTwoMatrixEquivOfRightInverse (coreRank h) A B hAB
  obtain ⟨Psi, hPsi⟩ := exists_nFullFrameRealizes_of_headFixed_initialBasis ha e
    (freeTwoMatrixEquivOfRightInverse_gen_of_column (coreRank h) A B hAB 0 hhead)
    (fun i => freeNOrientation_matrixEquiv alpha h A B hAB hchi _)
    (by simpa only [e, freeTwoMatrixEquivOfRightInverse_gen] using herror)
  refine ⟨Psi, hPsi.1, ?_⟩
  intro i
  have hi : nPhiHom ha h (abMk (Psi (dnGen alpha h i))) =
      nPhiHom ha h (abMk (freeNProjection alpha h (e (freeTwoRankGen (coreRank h) i)))) :=
    hPsi.2 i
  rw [show e (freeTwoRankGen (coreRank h) i) =
    freeTwoCoordinateWord (coreRank h) (fun j => A j i) from
      freeTwoMatrixEquivOfRightInverse_gen (coreRank h) A B hAB i,
    freeNProjection_ab_coordinateWord] at hi
  exact hi

#print axioms exists_nFullFrameRealizes_of_initialBasis
#print axioms exists_nFullFrameRealizes_of_headFixed_initialBasis
#print axioms freeNProjection_ab_coordinateWord
#print axioms exists_nFullFrameRealizes_of_matrix_initial_error

end
end GQ2.Dyadic.MarkedCore
