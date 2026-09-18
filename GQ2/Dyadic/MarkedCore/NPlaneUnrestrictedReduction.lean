import GQ2.Dyadic.MarkedCore.NPlaneRelativeRefinement
import GQ2.Dyadic.MarkedCore.FreeProTwoBasisCorrection
import GQ2.Dyadic.MarkedCore.NPlaneFreeStageTransfer

/-!
# The single unrestricted-stage input for strong N scaling

This file is a conditional reduction, not a producer of its hypothesis.
The input requests corrections in the orientation kernel, with no ordinary
row restrictions. The proved relative refinement restores the exact rows;
free-basis persistence, quotient transport and compactness then finish.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

/-- The remaining uniform image question. In particular, no ordinary-row
vanishing, diagonal hypothesis or compatible choice of stages is assumed. -/
def NUnrestrictedStageSupply (alpha h : ℕ) : Prop :=
  ∀ n : ℕ, ∀ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type),
    (∀ i, freeNOrientation alpha h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation alpha h (freeTwoRankGen (coreRank h) i)) →
    nRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (nRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+3) →
    ∃ t : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
      (∀ i, freeNOrientation alpha h (t i) = 1) ∧
      nRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)*t i) *
        (nRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
          twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4)

private theorem nUnitDiagonal_head_row {alpha h : ℕ} (kappa : ℤ_[2]ˣ)
    (y : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hy : ∀ j v, toAdd (freeTwoCoordinate (coreRank h) j (y v)) =
      if j=v then (freeTwoUnitPowerWeights (coreRank h) 2 kappa v : ℤ_[2]) else 0)
    (f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) (Multiplicative ℤ_[2])) :
    f (nRelWord alpha y) = f (nRelWord alpha (freeTwoRankGen (coreRank h))) := by
  apply toAdd.injective
  rw [nRelWord_ordinary_row, nRelWord_ordinary_row]
  congr 1
  rw [freeTwo_character_coordinates]
  simp only [hy, freeTwoUnitPowerWeights]
  have h02 : (0 : Fin (coreRank h)) ≠ 2 := nCoreZero_ne_two
  simp [h02]

/-- Uniform exact-row free stages follow from the unrestricted supply.
Only the displayed supply remains conditional. -/
theorem exists_nFree_exact_stage {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (H : NUnrestrictedStageSupply alpha h) (kappa : ℤ_[2]ˣ) (n : ℕ) :
    ∃ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
        (FreeTwoRank (coreRank h) : Type),
      (∀ i, freeNOrientation alpha h (e (freeTwoRankGen (coreRank h) i)) =
        freeNOrientation alpha h (freeTwoRankGen (coreRank h) i)) ∧
      (∀ j v, toAdd (freeTwoCoordinate (coreRank h) j
          (e (freeTwoRankGen (coreRank h) v))) =
        if j=v then (freeTwoUnitPowerWeights (coreRank h) 2 kappa v : ℤ_[2]) else 0) ∧
      nRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)) *
        (nRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
          twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+3) := by
  induction n with
  | zero =>
    refine ⟨freeTwoUnitPowerEquiv (coreRank h) 2 kappa, ?_, ?_, ?_⟩
    · intro i
      exact freeNOrientation_unitPowerEquiv alpha h 2 nCoreTwo_ne_one kappa _
    · intro j v
      rw [freeTwoUnitPowerEquiv_gen]
      exact freeTwoUnitPowerMark_coordinate _ _ _ _ _
    · simpa only [freeTwoUnitPowerEquiv_gen, nInitialUnitPowerError] using
        nInitialUnitPowerError_mem_three alpha h 2 (Ne.symm nCoreZero_ne_two) kappa
  | succ n ih =>
    obtain ⟨e, hechi, hediag, heerror⟩ := ih
    obtain ⟨t, ht, htchi, hterror⟩ := H n e hechi heerror
    obtain ⟨s, hs, hschi, hsrow, hserror⟩ := exists_nPlane_relative_correction halpha n
      (fun i => e (freeTwoRankGen (coreRank h) i)) t
      (freeTwoUnitPowerWeights (coreRank h) 2 kappa) hediag
      (nRelWord alpha (freeTwoRankGen (coreRank h)))
      (nUnitDiagonal_head_row kappa _ hediag) ht htchi hterror
    obtain ⟨e', he'⟩ := exists_freeTwoBasisCorrection (coreRank h) e s
      (fun i => twoCentralSeries_antitone (G := (FreeTwoRank (coreRank h) : Type))
        (by omega : 2 ≤ n+2) (hs i))
    refine ⟨e', ?_, ?_, ?_⟩
    · intro i
      rw [he', map_mul, hschi, mul_one, hechi]
    · intro j v
      rw [he', map_mul, hsrow, mul_one]
      exact hediag j v
    · have htuple : (fun i => e' (freeTwoRankGen (coreRank h) i)) =
          (fun i => e (freeTwoRankGen (coreRank h) i)) * s := funext he'
      rw [htuple, show n+1+3=n+4 by omega]
      exact hserror

/-- The sole remaining input is the unrestricted orientation-kernel stage
supply. All simultaneous ordinary rows, quotient transport and limiting
automorphism construction are proved in the implication. -/
theorem nPlaneScalingHypothesis_of_unrestrictedStageSupply {alpha h : ℕ}
    (halpha : 2 ≤ alpha) (H : NUnrestrictedStageSupply alpha h) :
    NPlaneScalingHypothesis alpha h := by
  apply (nPlaneScalingHypothesis_iff_stages alpha h).mpr
  intro kappa k
  obtain ⟨e, hechi, hediag, heerror⟩ := exists_nFree_exact_stage halpha H kappa k
  refine ⟨fun i => freeNProjection alpha h (e (freeTwoRankGen (coreRank h) i)), ?_⟩
  exact nPlaneStageSet_antitone alpha h (nPlaneDet kappa) (by omega : k ≤ k+3)
    (nPlaneStageSet_of_free_exact_stage alpha h (k+3) kappa e hechi hediag heerror)

#print axioms NUnrestrictedStageSupply
#print axioms exists_nFree_exact_stage
#print axioms nPlaneScalingHypothesis_of_unrestrictedStageSupply

end
end GQ2.Dyadic.MarkedCore
