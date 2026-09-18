import GQ2.Dyadic.MarkedCore.NPlaneFullRelativeRefinement
import GQ2.Dyadic.MarkedCore.NPlaneAmbientStage
import GQ2.Dyadic.MarkedCore.FreeProTwoBasisCorrection
import GQ2.Dyadic.MarkedCore.NPlaneFreeStageTransfer
import GQ2.Dyadic.MarkedCore.ClearWide

/-!
# Strong N-plane scaling in arbitrary rank

This proof uses fully ambient corrections with no orientation or ordinary
row restrictions. The proved relative refinement restores the exact rows;
free-basis persistence, quotient transport and compactness then finish.
The generic image criterion supplies the ambient corrections, so the final
scaling, GL₂ and admissible stabilizer theorems have no stage-supply premise.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

/-- The uniform ambient image property. In particular, no ordinary-row
vanishing, diagonal hypothesis or compatible choice of stages is assumed. -/
def NAmbientStageSupply (alpha h : ℕ) : Prop :=
  ∀ n : ℕ, ∀ e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type),
    (∀ i, freeNOrientation alpha h (e (freeTwoRankGen (coreRank h) i)) =
      freeNOrientation alpha h (freeTwoRankGen (coreRank h) i)) →
    nRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i)) *
      (nRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+3) →
    ∃ t : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
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

/-- Uniform exact-row free stages follow from ambient correction supply.
The supply is proved below by the generic image criterion. -/
theorem exists_nFree_exact_stage_ambient {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (H : NAmbientStageSupply alpha h) (kappa : ℤ_[2]ˣ) (n : ℕ) :
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
    obtain ⟨t, ht, hterror⟩ := H n e hechi heerror
    obtain ⟨s, hs, hschi, hsrow, hserror⟩ := exists_nPlane_full_relative_correction halpha n
      (fun i => e (freeTwoRankGen (coreRank h) i)) t
      (freeTwoUnitPowerWeights (coreRank h) 2 kappa) hediag
      (nRelWord alpha (freeTwoRankGen (coreRank h)))
      (nUnitDiagonal_head_row kappa _ hediag) ht hterror
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

/-- Ambient correction supply suffices: simultaneous ordinary rows, orientation,
quotient transport and the limiting automorphism are restored in the proof. -/
theorem nPlaneScalingHypothesis_of_ambientStageSupply {alpha h : ℕ}
    (halpha : 2 ≤ alpha) (H : NAmbientStageSupply alpha h) :
    NPlaneScalingHypothesis alpha h := by
  apply (nPlaneScalingHypothesis_iff_stages alpha h).mpr
  intro kappa k
  obtain ⟨e, hechi, hediag, heerror⟩ := exists_nFree_exact_stage_ambient halpha H kappa k
  refine ⟨fun i => freeNProjection alpha h (e (freeTwoRankGen (coreRank h) i)), ?_⟩
  exact nPlaneStageSet_antitone alpha h (nPlaneDet kappa) (by omega : k ≤ k+3)
    (nPlaneStageSet_of_free_exact_stage alpha h (k+3) kappa e hechi hediag heerror)

/-- The generic ambient image criterion supplies the previously conditional
input, at every rank and every correction depth. -/
theorem nAmbientStageSupply {alpha h : ℕ} (halpha : 2 ≤ alpha) :
    NAmbientStageSupply alpha h := by
  intro n e he herr
  have H := NPlaneAmbientStage.exists_ambient_stage halpha (by omega : 3 ≤ n+3) e he herr
  simpa only [show n+3-1=n+2 by omega, show n+3+1=n+4 by omega] using H

/-- Strong simultaneous integral N-plane scaling, uniformly in all valid
exponents and all handle ranks. No additional scaling or stage input. -/
theorem nPlaneScalingHypothesis_general {alpha h : ℕ} (halpha : 2 ≤ alpha) :
    NPlaneScalingHypothesis alpha h :=
  nPlaneScalingHypothesis_of_ambientStageSupply halpha (nAmbientStageSupply halpha)

theorem nCorePlane_gl2_lift_general {alpha h : ℕ} (halpha : 2 ≤ alpha)
    {T : Matrix (Fin 2) (Fin 2) ℤ_[2]} (hT : IsUnit T.det) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      NPlaneRealizes alpha h Psi T :=
  nCorePlane_gl2_lift alpha h (nPlaneScalingHypothesis_general halpha) hT

/-- Every admissible N stabilizer parameter has its simultaneous integral
character-frame action realized by one orientation-preserving automorphism. -/
theorem nStabParam_lift_general {alpha h : ℕ} (halpha : 2 ≤ alpha)
    {P : NStabParam} (hP : P.Admissible) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
      ∀ f : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]),
        nuFrame f (fun i => Psi (dnGen alpha h i)) = P.nuAction (nuFrame f (dnGen alpha h)) :=
  nStabParam_lift_of_scaling alpha h (nPlaneScalingHypothesis_general halpha) hP

#print axioms NAmbientStageSupply
#print axioms exists_nFree_exact_stage_ambient
#print axioms nPlaneScalingHypothesis_of_ambientStageSupply
#print axioms nAmbientStageSupply
#print axioms nPlaneScalingHypothesis_general
#print axioms nCorePlane_gl2_lift_general
#print axioms nStabParam_lift_general

end
end GQ2.Dyadic.MarkedCore
